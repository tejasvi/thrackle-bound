import Thrackle78Facts.T337.HS150
import Thrackle78Facts.T337.HS151
import Thrackle78Facts.T337.HS152
import Thrackle78Facts.T337.HS153
import Thrackle78Facts.T337.HS154
import Thrackle78Facts.T337.HS155
import Thrackle78Facts.T337.HS156
import Thrackle78Facts.T337.HS157
import Thrackle78Facts.T337.HS158
import Thrackle78Facts.T337.HS159
import Thrackle78Facts.T337.HS160
import Thrackle78Facts.T337.HS161
import Thrackle78Facts.T337.HS162
import Thrackle78Facts.T337.HS163
import Thrackle78Facts.T337.HS164
import Thrackle78Facts.T337.HS165
import Thrackle78Facts.T337.HS166
import Thrackle78Facts.T337.HS167
import Thrackle78Facts.T337.HS168
import Thrackle78Facts.T337.HS169
import Thrackle78Facts.T337.HS170
import Thrackle78Facts.T337.HS171
import Thrackle78Facts.T337.HS172
import Thrackle78Facts.T337.HS173
import Thrackle78Facts.T337.HS174
import Thrackle78Facts.T337.HS175
import Thrackle78Facts.T337.HS176
import Thrackle78Facts.T337.HS177
import Thrackle78Facts.T337.HS178
import Thrackle78Facts.T337.HS179

open Thrackle78 Thrackle78Core

theorem T78Native.T337.hgroup_ok_5 : ∀ j < 30, checkFilterXShardsF 12 lTH337.toArray T78Native.T337.c10aX T78Native.T337.dlook T78Native.T337.orcF T78Native.T337.famOrcF T78Native.T337.adaptF (T78Native.T337.hbatch (30 * 5 + j)) = true := by
  intro j hj
  interval_cases j
  exacts [T78Native.T337.hshard_ok_150,
      T78Native.T337.hshard_ok_151,
      T78Native.T337.hshard_ok_152,
      T78Native.T337.hshard_ok_153,
      T78Native.T337.hshard_ok_154,
      T78Native.T337.hshard_ok_155,
      T78Native.T337.hshard_ok_156,
      T78Native.T337.hshard_ok_157,
      T78Native.T337.hshard_ok_158,
      T78Native.T337.hshard_ok_159,
      T78Native.T337.hshard_ok_160,
      T78Native.T337.hshard_ok_161,
      T78Native.T337.hshard_ok_162,
      T78Native.T337.hshard_ok_163,
      T78Native.T337.hshard_ok_164,
      T78Native.T337.hshard_ok_165,
      T78Native.T337.hshard_ok_166,
      T78Native.T337.hshard_ok_167,
      T78Native.T337.hshard_ok_168,
      T78Native.T337.hshard_ok_169,
      T78Native.T337.hshard_ok_170,
      T78Native.T337.hshard_ok_171,
      T78Native.T337.hshard_ok_172,
      T78Native.T337.hshard_ok_173,
      T78Native.T337.hshard_ok_174,
      T78Native.T337.hshard_ok_175,
      T78Native.T337.hshard_ok_176,
      T78Native.T337.hshard_ok_177,
      T78Native.T337.hshard_ok_178,
      T78Native.T337.hshard_ok_179]
