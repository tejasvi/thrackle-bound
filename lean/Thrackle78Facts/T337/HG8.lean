import Thrackle78Facts.T337.HS240
import Thrackle78Facts.T337.HS241
import Thrackle78Facts.T337.HS242
import Thrackle78Facts.T337.HS243
import Thrackle78Facts.T337.HS244
import Thrackle78Facts.T337.HS245
import Thrackle78Facts.T337.HS246
import Thrackle78Facts.T337.HS247
import Thrackle78Facts.T337.HS248
import Thrackle78Facts.T337.HS249
import Thrackle78Facts.T337.HS250
import Thrackle78Facts.T337.HS251
import Thrackle78Facts.T337.HS252
import Thrackle78Facts.T337.HS253
import Thrackle78Facts.T337.HS254
import Thrackle78Facts.T337.HS255
import Thrackle78Facts.T337.HS256
import Thrackle78Facts.T337.HS257
import Thrackle78Facts.T337.HS258
import Thrackle78Facts.T337.HS259
import Thrackle78Facts.T337.HS260
import Thrackle78Facts.T337.HS261
import Thrackle78Facts.T337.HS262
import Thrackle78Facts.T337.HS263
import Thrackle78Facts.T337.HS264
import Thrackle78Facts.T337.HS265
import Thrackle78Facts.T337.HS266
import Thrackle78Facts.T337.HS267
import Thrackle78Facts.T337.HS268
import Thrackle78Facts.T337.HS269

open Thrackle78 Thrackle78Core

theorem T78Native.T337.hgroup_ok_8 : ∀ j < 30, checkFilterXShardsF 12 lTH337.toArray T78Native.T337.c10aX T78Native.T337.dlook T78Native.T337.orcF T78Native.T337.famOrcF T78Native.T337.adaptF (T78Native.T337.hbatch (30 * 8 + j)) = true := by
  intro j hj
  interval_cases j
  exacts [T78Native.T337.hshard_ok_240,
      T78Native.T337.hshard_ok_241,
      T78Native.T337.hshard_ok_242,
      T78Native.T337.hshard_ok_243,
      T78Native.T337.hshard_ok_244,
      T78Native.T337.hshard_ok_245,
      T78Native.T337.hshard_ok_246,
      T78Native.T337.hshard_ok_247,
      T78Native.T337.hshard_ok_248,
      T78Native.T337.hshard_ok_249,
      T78Native.T337.hshard_ok_250,
      T78Native.T337.hshard_ok_251,
      T78Native.T337.hshard_ok_252,
      T78Native.T337.hshard_ok_253,
      T78Native.T337.hshard_ok_254,
      T78Native.T337.hshard_ok_255,
      T78Native.T337.hshard_ok_256,
      T78Native.T337.hshard_ok_257,
      T78Native.T337.hshard_ok_258,
      T78Native.T337.hshard_ok_259,
      T78Native.T337.hshard_ok_260,
      T78Native.T337.hshard_ok_261,
      T78Native.T337.hshard_ok_262,
      T78Native.T337.hshard_ok_263,
      T78Native.T337.hshard_ok_264,
      T78Native.T337.hshard_ok_265,
      T78Native.T337.hshard_ok_266,
      T78Native.T337.hshard_ok_267,
      T78Native.T337.hshard_ok_268,
      T78Native.T337.hshard_ok_269]
