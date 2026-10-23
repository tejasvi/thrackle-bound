import Thrackle78Facts.T337.HS510
import Thrackle78Facts.T337.HS511
import Thrackle78Facts.T337.HS512
import Thrackle78Facts.T337.HS513
import Thrackle78Facts.T337.HS514
import Thrackle78Facts.T337.HS515
import Thrackle78Facts.T337.HS516
import Thrackle78Facts.T337.HS517
import Thrackle78Facts.T337.HS518
import Thrackle78Facts.T337.HS519
import Thrackle78Facts.T337.HS520
import Thrackle78Facts.T337.HS521
import Thrackle78Facts.T337.HS522
import Thrackle78Facts.T337.HS523
import Thrackle78Facts.T337.HS524
import Thrackle78Facts.T337.HS525
import Thrackle78Facts.T337.HS526
import Thrackle78Facts.T337.HS527
import Thrackle78Facts.T337.HS528
import Thrackle78Facts.T337.HS529
import Thrackle78Facts.T337.HS530
import Thrackle78Facts.T337.HS531
import Thrackle78Facts.T337.HS532
import Thrackle78Facts.T337.HS533
import Thrackle78Facts.T337.HS534
import Thrackle78Facts.T337.HS535
import Thrackle78Facts.T337.HS536
import Thrackle78Facts.T337.HS537
import Thrackle78Facts.T337.HS538
import Thrackle78Facts.T337.HS539

open Thrackle78 Thrackle78Core

theorem T78Native.T337.hgroup_ok_17 : ∀ j < 30, checkFilterXShardsF 12 lTH337.toArray T78Native.T337.c10aX T78Native.T337.dlook T78Native.T337.orcF T78Native.T337.famOrcF T78Native.T337.adaptF (T78Native.T337.hbatch (30 * 17 + j)) = true := by
  intro j hj
  interval_cases j
  exacts [T78Native.T337.hshard_ok_510,
      T78Native.T337.hshard_ok_511,
      T78Native.T337.hshard_ok_512,
      T78Native.T337.hshard_ok_513,
      T78Native.T337.hshard_ok_514,
      T78Native.T337.hshard_ok_515,
      T78Native.T337.hshard_ok_516,
      T78Native.T337.hshard_ok_517,
      T78Native.T337.hshard_ok_518,
      T78Native.T337.hshard_ok_519,
      T78Native.T337.hshard_ok_520,
      T78Native.T337.hshard_ok_521,
      T78Native.T337.hshard_ok_522,
      T78Native.T337.hshard_ok_523,
      T78Native.T337.hshard_ok_524,
      T78Native.T337.hshard_ok_525,
      T78Native.T337.hshard_ok_526,
      T78Native.T337.hshard_ok_527,
      T78Native.T337.hshard_ok_528,
      T78Native.T337.hshard_ok_529,
      T78Native.T337.hshard_ok_530,
      T78Native.T337.hshard_ok_531,
      T78Native.T337.hshard_ok_532,
      T78Native.T337.hshard_ok_533,
      T78Native.T337.hshard_ok_534,
      T78Native.T337.hshard_ok_535,
      T78Native.T337.hshard_ok_536,
      T78Native.T337.hshard_ok_537,
      T78Native.T337.hshard_ok_538,
      T78Native.T337.hshard_ok_539]
