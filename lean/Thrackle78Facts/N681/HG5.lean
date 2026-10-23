import Thrackle78Facts.N681.HS150
import Thrackle78Facts.N681.HS151
import Thrackle78Facts.N681.HS152
import Thrackle78Facts.N681.HS153
import Thrackle78Facts.N681.HS154
import Thrackle78Facts.N681.HS155
import Thrackle78Facts.N681.HS156
import Thrackle78Facts.N681.HS157
import Thrackle78Facts.N681.HS158
import Thrackle78Facts.N681.HS159
import Thrackle78Facts.N681.HS160
import Thrackle78Facts.N681.HS161
import Thrackle78Facts.N681.HS162
import Thrackle78Facts.N681.HS163
import Thrackle78Facts.N681.HS164
import Thrackle78Facts.N681.HS165
import Thrackle78Facts.N681.HS166
import Thrackle78Facts.N681.HS167
import Thrackle78Facts.N681.HS168
import Thrackle78Facts.N681.HS169
import Thrackle78Facts.N681.HS170
import Thrackle78Facts.N681.HS171
import Thrackle78Facts.N681.HS172
import Thrackle78Facts.N681.HS173
import Thrackle78Facts.N681.HS174
import Thrackle78Facts.N681.HS175
import Thrackle78Facts.N681.HS176
import Thrackle78Facts.N681.HS177
import Thrackle78Facts.N681.HS178
import Thrackle78Facts.N681.HS179

open Thrackle78 Thrackle78Core

theorem T78Native.N681.hgroup_ok_5 : ∀ j < 30, checkFilterXShards 12 lDB681.toArray T78Native.N681.h12X T78Native.N681.h12look T78Native.N681.orcF (T78Native.N681.hbatch (30 * 5 + j)) = true := by
  intro j hj
  interval_cases j
  exacts [T78Native.N681.hshard_ok_150,
      T78Native.N681.hshard_ok_151,
      T78Native.N681.hshard_ok_152,
      T78Native.N681.hshard_ok_153,
      T78Native.N681.hshard_ok_154,
      T78Native.N681.hshard_ok_155,
      T78Native.N681.hshard_ok_156,
      T78Native.N681.hshard_ok_157,
      T78Native.N681.hshard_ok_158,
      T78Native.N681.hshard_ok_159,
      T78Native.N681.hshard_ok_160,
      T78Native.N681.hshard_ok_161,
      T78Native.N681.hshard_ok_162,
      T78Native.N681.hshard_ok_163,
      T78Native.N681.hshard_ok_164,
      T78Native.N681.hshard_ok_165,
      T78Native.N681.hshard_ok_166,
      T78Native.N681.hshard_ok_167,
      T78Native.N681.hshard_ok_168,
      T78Native.N681.hshard_ok_169,
      T78Native.N681.hshard_ok_170,
      T78Native.N681.hshard_ok_171,
      T78Native.N681.hshard_ok_172,
      T78Native.N681.hshard_ok_173,
      T78Native.N681.hshard_ok_174,
      T78Native.N681.hshard_ok_175,
      T78Native.N681.hshard_ok_176,
      T78Native.N681.hshard_ok_177,
      T78Native.N681.hshard_ok_178,
      T78Native.N681.hshard_ok_179]
