import Thrackle78Facts.T337.HS360
import Thrackle78Facts.T337.HS361
import Thrackle78Facts.T337.HS362
import Thrackle78Facts.T337.HS363
import Thrackle78Facts.T337.HS364
import Thrackle78Facts.T337.HS365
import Thrackle78Facts.T337.HS366
import Thrackle78Facts.T337.HS367
import Thrackle78Facts.T337.HS368
import Thrackle78Facts.T337.HS369
import Thrackle78Facts.T337.HS370
import Thrackle78Facts.T337.HS371
import Thrackle78Facts.T337.HS372
import Thrackle78Facts.T337.HS373
import Thrackle78Facts.T337.HS374
import Thrackle78Facts.T337.HS375
import Thrackle78Facts.T337.HS376
import Thrackle78Facts.T337.HS377
import Thrackle78Facts.T337.HS378
import Thrackle78Facts.T337.HS379
import Thrackle78Facts.T337.HS380
import Thrackle78Facts.T337.HS381
import Thrackle78Facts.T337.HS382
import Thrackle78Facts.T337.HS383
import Thrackle78Facts.T337.HS384
import Thrackle78Facts.T337.HS385
import Thrackle78Facts.T337.HS386
import Thrackle78Facts.T337.HS387
import Thrackle78Facts.T337.HS388
import Thrackle78Facts.T337.HS389

open Thrackle78 Thrackle78Core

theorem T78Native.T337.hgroup_ok_12 : ∀ j < 30, checkFilterXShardsF 12 lTH337.toArray T78Native.T337.c10aX T78Native.T337.dlook T78Native.T337.orcF T78Native.T337.famOrcF T78Native.T337.adaptF (T78Native.T337.hbatch (30 * 12 + j)) = true := by
  intro j hj
  interval_cases j
  exacts [T78Native.T337.hshard_ok_360,
      T78Native.T337.hshard_ok_361,
      T78Native.T337.hshard_ok_362,
      T78Native.T337.hshard_ok_363,
      T78Native.T337.hshard_ok_364,
      T78Native.T337.hshard_ok_365,
      T78Native.T337.hshard_ok_366,
      T78Native.T337.hshard_ok_367,
      T78Native.T337.hshard_ok_368,
      T78Native.T337.hshard_ok_369,
      T78Native.T337.hshard_ok_370,
      T78Native.T337.hshard_ok_371,
      T78Native.T337.hshard_ok_372,
      T78Native.T337.hshard_ok_373,
      T78Native.T337.hshard_ok_374,
      T78Native.T337.hshard_ok_375,
      T78Native.T337.hshard_ok_376,
      T78Native.T337.hshard_ok_377,
      T78Native.T337.hshard_ok_378,
      T78Native.T337.hshard_ok_379,
      T78Native.T337.hshard_ok_380,
      T78Native.T337.hshard_ok_381,
      T78Native.T337.hshard_ok_382,
      T78Native.T337.hshard_ok_383,
      T78Native.T337.hshard_ok_384,
      T78Native.T337.hshard_ok_385,
      T78Native.T337.hshard_ok_386,
      T78Native.T337.hshard_ok_387,
      T78Native.T337.hshard_ok_388,
      T78Native.T337.hshard_ok_389]
