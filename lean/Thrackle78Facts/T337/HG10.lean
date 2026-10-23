import Thrackle78Facts.T337.HS300
import Thrackle78Facts.T337.HS301
import Thrackle78Facts.T337.HS302
import Thrackle78Facts.T337.HS303
import Thrackle78Facts.T337.HS304
import Thrackle78Facts.T337.HS305
import Thrackle78Facts.T337.HS306
import Thrackle78Facts.T337.HS307
import Thrackle78Facts.T337.HS308
import Thrackle78Facts.T337.HS309
import Thrackle78Facts.T337.HS310
import Thrackle78Facts.T337.HS311
import Thrackle78Facts.T337.HS312
import Thrackle78Facts.T337.HS313
import Thrackle78Facts.T337.HS314
import Thrackle78Facts.T337.HS315
import Thrackle78Facts.T337.HS316
import Thrackle78Facts.T337.HS317
import Thrackle78Facts.T337.HS318
import Thrackle78Facts.T337.HS319
import Thrackle78Facts.T337.HS320
import Thrackle78Facts.T337.HS321
import Thrackle78Facts.T337.HS322
import Thrackle78Facts.T337.HS323
import Thrackle78Facts.T337.HS324
import Thrackle78Facts.T337.HS325
import Thrackle78Facts.T337.HS326
import Thrackle78Facts.T337.HS327
import Thrackle78Facts.T337.HS328
import Thrackle78Facts.T337.HS329

open Thrackle78 Thrackle78Core

theorem T78Native.T337.hgroup_ok_10 : ∀ j < 30, checkFilterXShardsF 12 lTH337.toArray T78Native.T337.c10aX T78Native.T337.dlook T78Native.T337.orcF T78Native.T337.famOrcF T78Native.T337.adaptF (T78Native.T337.hbatch (30 * 10 + j)) = true := by
  intro j hj
  interval_cases j
  exacts [T78Native.T337.hshard_ok_300,
      T78Native.T337.hshard_ok_301,
      T78Native.T337.hshard_ok_302,
      T78Native.T337.hshard_ok_303,
      T78Native.T337.hshard_ok_304,
      T78Native.T337.hshard_ok_305,
      T78Native.T337.hshard_ok_306,
      T78Native.T337.hshard_ok_307,
      T78Native.T337.hshard_ok_308,
      T78Native.T337.hshard_ok_309,
      T78Native.T337.hshard_ok_310,
      T78Native.T337.hshard_ok_311,
      T78Native.T337.hshard_ok_312,
      T78Native.T337.hshard_ok_313,
      T78Native.T337.hshard_ok_314,
      T78Native.T337.hshard_ok_315,
      T78Native.T337.hshard_ok_316,
      T78Native.T337.hshard_ok_317,
      T78Native.T337.hshard_ok_318,
      T78Native.T337.hshard_ok_319,
      T78Native.T337.hshard_ok_320,
      T78Native.T337.hshard_ok_321,
      T78Native.T337.hshard_ok_322,
      T78Native.T337.hshard_ok_323,
      T78Native.T337.hshard_ok_324,
      T78Native.T337.hshard_ok_325,
      T78Native.T337.hshard_ok_326,
      T78Native.T337.hshard_ok_327,
      T78Native.T337.hshard_ok_328,
      T78Native.T337.hshard_ok_329]
