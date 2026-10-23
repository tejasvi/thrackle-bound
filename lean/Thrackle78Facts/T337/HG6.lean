import Thrackle78Facts.T337.HS180
import Thrackle78Facts.T337.HS181
import Thrackle78Facts.T337.HS182
import Thrackle78Facts.T337.HS183
import Thrackle78Facts.T337.HS184
import Thrackle78Facts.T337.HS185
import Thrackle78Facts.T337.HS186
import Thrackle78Facts.T337.HS187
import Thrackle78Facts.T337.HS188
import Thrackle78Facts.T337.HS189
import Thrackle78Facts.T337.HS190
import Thrackle78Facts.T337.HS191
import Thrackle78Facts.T337.HS192
import Thrackle78Facts.T337.HS193
import Thrackle78Facts.T337.HS194
import Thrackle78Facts.T337.HS195
import Thrackle78Facts.T337.HS196
import Thrackle78Facts.T337.HS197
import Thrackle78Facts.T337.HS198
import Thrackle78Facts.T337.HS199
import Thrackle78Facts.T337.HS200
import Thrackle78Facts.T337.HS201
import Thrackle78Facts.T337.HS202
import Thrackle78Facts.T337.HS203
import Thrackle78Facts.T337.HS204
import Thrackle78Facts.T337.HS205
import Thrackle78Facts.T337.HS206
import Thrackle78Facts.T337.HS207
import Thrackle78Facts.T337.HS208
import Thrackle78Facts.T337.HS209

open Thrackle78 Thrackle78Core

theorem T78Native.T337.hgroup_ok_6 : ∀ j < 30, checkFilterXShardsF 12 lTH337.toArray T78Native.T337.c10aX T78Native.T337.dlook T78Native.T337.orcF T78Native.T337.famOrcF T78Native.T337.adaptF (T78Native.T337.hbatch (30 * 6 + j)) = true := by
  intro j hj
  interval_cases j
  exacts [T78Native.T337.hshard_ok_180,
      T78Native.T337.hshard_ok_181,
      T78Native.T337.hshard_ok_182,
      T78Native.T337.hshard_ok_183,
      T78Native.T337.hshard_ok_184,
      T78Native.T337.hshard_ok_185,
      T78Native.T337.hshard_ok_186,
      T78Native.T337.hshard_ok_187,
      T78Native.T337.hshard_ok_188,
      T78Native.T337.hshard_ok_189,
      T78Native.T337.hshard_ok_190,
      T78Native.T337.hshard_ok_191,
      T78Native.T337.hshard_ok_192,
      T78Native.T337.hshard_ok_193,
      T78Native.T337.hshard_ok_194,
      T78Native.T337.hshard_ok_195,
      T78Native.T337.hshard_ok_196,
      T78Native.T337.hshard_ok_197,
      T78Native.T337.hshard_ok_198,
      T78Native.T337.hshard_ok_199,
      T78Native.T337.hshard_ok_200,
      T78Native.T337.hshard_ok_201,
      T78Native.T337.hshard_ok_202,
      T78Native.T337.hshard_ok_203,
      T78Native.T337.hshard_ok_204,
      T78Native.T337.hshard_ok_205,
      T78Native.T337.hshard_ok_206,
      T78Native.T337.hshard_ok_207,
      T78Native.T337.hshard_ok_208,
      T78Native.T337.hshard_ok_209]
