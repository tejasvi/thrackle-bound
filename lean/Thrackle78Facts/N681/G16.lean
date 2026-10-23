import Thrackle78Facts.N681.B640
import Thrackle78Facts.N681.B641
import Thrackle78Facts.N681.B642
import Thrackle78Facts.N681.B643
import Thrackle78Facts.N681.B644
import Thrackle78Facts.N681.B645
import Thrackle78Facts.N681.B646
import Thrackle78Facts.N681.B647
import Thrackle78Facts.N681.B648
import Thrackle78Facts.N681.B649
import Thrackle78Facts.N681.B650
import Thrackle78Facts.N681.B651
import Thrackle78Facts.N681.B652
import Thrackle78Facts.N681.B653
import Thrackle78Facts.N681.B654
import Thrackle78Facts.N681.B655
import Thrackle78Facts.N681.B656
import Thrackle78Facts.N681.B657
import Thrackle78Facts.N681.B658
import Thrackle78Facts.N681.B659
import Thrackle78Facts.N681.B660
import Thrackle78Facts.N681.B661
import Thrackle78Facts.N681.B662
import Thrackle78Facts.N681.B663
import Thrackle78Facts.N681.B664
import Thrackle78Facts.N681.B665
import Thrackle78Facts.N681.B666
import Thrackle78Facts.N681.B667
import Thrackle78Facts.N681.B668
import Thrackle78Facts.N681.B669
import Thrackle78Facts.N681.B670
import Thrackle78Facts.N681.B671
import Thrackle78Facts.N681.B672
import Thrackle78Facts.N681.B673
import Thrackle78Facts.N681.B674
import Thrackle78Facts.N681.B675
import Thrackle78Facts.N681.B676
import Thrackle78Facts.N681.B677
import Thrackle78Facts.N681.B678
import Thrackle78Facts.N681.B679

open Thrackle78 Thrackle78Core

theorem T78Native.N681.group_ok_16 : ∀ j < 40, checkBFromListRX 12 lDB681.toArray T78Native.N681.fsX (T78Native.N681.orcF lDB681.toArray) (T78Native.N681.famOrcF lDB681.toArray) (T78Native.N681.adaptF lDB681.toArray) (T78Native.N681.batch (40 * 16 + j)) = true := by
  intro j hj
  interval_cases j
  exacts [T78Native.N681.batch_ok_640,
      T78Native.N681.batch_ok_641,
      T78Native.N681.batch_ok_642,
      T78Native.N681.batch_ok_643,
      T78Native.N681.batch_ok_644,
      T78Native.N681.batch_ok_645,
      T78Native.N681.batch_ok_646,
      T78Native.N681.batch_ok_647,
      T78Native.N681.batch_ok_648,
      T78Native.N681.batch_ok_649,
      T78Native.N681.batch_ok_650,
      T78Native.N681.batch_ok_651,
      T78Native.N681.batch_ok_652,
      T78Native.N681.batch_ok_653,
      T78Native.N681.batch_ok_654,
      T78Native.N681.batch_ok_655,
      T78Native.N681.batch_ok_656,
      T78Native.N681.batch_ok_657,
      T78Native.N681.batch_ok_658,
      T78Native.N681.batch_ok_659,
      T78Native.N681.batch_ok_660,
      T78Native.N681.batch_ok_661,
      T78Native.N681.batch_ok_662,
      T78Native.N681.batch_ok_663,
      T78Native.N681.batch_ok_664,
      T78Native.N681.batch_ok_665,
      T78Native.N681.batch_ok_666,
      T78Native.N681.batch_ok_667,
      T78Native.N681.batch_ok_668,
      T78Native.N681.batch_ok_669,
      T78Native.N681.batch_ok_670,
      T78Native.N681.batch_ok_671,
      T78Native.N681.batch_ok_672,
      T78Native.N681.batch_ok_673,
      T78Native.N681.batch_ok_674,
      T78Native.N681.batch_ok_675,
      T78Native.N681.batch_ok_676,
      T78Native.N681.batch_ok_677,
      T78Native.N681.batch_ok_678,
      T78Native.N681.batch_ok_679]
