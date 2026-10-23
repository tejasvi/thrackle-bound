import Thrackle78Facts.T337.HS480
import Thrackle78Facts.T337.HS481
import Thrackle78Facts.T337.HS482
import Thrackle78Facts.T337.HS483
import Thrackle78Facts.T337.HS484
import Thrackle78Facts.T337.HS485
import Thrackle78Facts.T337.HS486
import Thrackle78Facts.T337.HS487
import Thrackle78Facts.T337.HS488
import Thrackle78Facts.T337.HS489
import Thrackle78Facts.T337.HS490
import Thrackle78Facts.T337.HS491
import Thrackle78Facts.T337.HS492
import Thrackle78Facts.T337.HS493
import Thrackle78Facts.T337.HS494
import Thrackle78Facts.T337.HS495
import Thrackle78Facts.T337.HS496
import Thrackle78Facts.T337.HS497
import Thrackle78Facts.T337.HS498
import Thrackle78Facts.T337.HS499
import Thrackle78Facts.T337.HS500
import Thrackle78Facts.T337.HS501
import Thrackle78Facts.T337.HS502
import Thrackle78Facts.T337.HS503
import Thrackle78Facts.T337.HS504
import Thrackle78Facts.T337.HS505
import Thrackle78Facts.T337.HS506
import Thrackle78Facts.T337.HS507
import Thrackle78Facts.T337.HS508
import Thrackle78Facts.T337.HS509

open Thrackle78 Thrackle78Core

theorem T78Native.T337.hgroup_ok_16 : ∀ j < 30, checkFilterXShardsF 12 lTH337.toArray T78Native.T337.c10aX T78Native.T337.dlook T78Native.T337.orcF T78Native.T337.famOrcF T78Native.T337.adaptF (T78Native.T337.hbatch (30 * 16 + j)) = true := by
  intro j hj
  interval_cases j
  exacts [T78Native.T337.hshard_ok_480,
      T78Native.T337.hshard_ok_481,
      T78Native.T337.hshard_ok_482,
      T78Native.T337.hshard_ok_483,
      T78Native.T337.hshard_ok_484,
      T78Native.T337.hshard_ok_485,
      T78Native.T337.hshard_ok_486,
      T78Native.T337.hshard_ok_487,
      T78Native.T337.hshard_ok_488,
      T78Native.T337.hshard_ok_489,
      T78Native.T337.hshard_ok_490,
      T78Native.T337.hshard_ok_491,
      T78Native.T337.hshard_ok_492,
      T78Native.T337.hshard_ok_493,
      T78Native.T337.hshard_ok_494,
      T78Native.T337.hshard_ok_495,
      T78Native.T337.hshard_ok_496,
      T78Native.T337.hshard_ok_497,
      T78Native.T337.hshard_ok_498,
      T78Native.T337.hshard_ok_499,
      T78Native.T337.hshard_ok_500,
      T78Native.T337.hshard_ok_501,
      T78Native.T337.hshard_ok_502,
      T78Native.T337.hshard_ok_503,
      T78Native.T337.hshard_ok_504,
      T78Native.T337.hshard_ok_505,
      T78Native.T337.hshard_ok_506,
      T78Native.T337.hshard_ok_507,
      T78Native.T337.hshard_ok_508,
      T78Native.T337.hshard_ok_509]
