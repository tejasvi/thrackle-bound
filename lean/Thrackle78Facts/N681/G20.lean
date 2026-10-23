import Thrackle78Facts.N681.B800
import Thrackle78Facts.N681.B801
import Thrackle78Facts.N681.B802
import Thrackle78Facts.N681.B803
import Thrackle78Facts.N681.B804
import Thrackle78Facts.N681.B805
import Thrackle78Facts.N681.B806
import Thrackle78Facts.N681.B807
import Thrackle78Facts.N681.B808
import Thrackle78Facts.N681.B809
import Thrackle78Facts.N681.B810
import Thrackle78Facts.N681.B811
import Thrackle78Facts.N681.B812
import Thrackle78Facts.N681.B813
import Thrackle78Facts.N681.B814
import Thrackle78Facts.N681.B815
import Thrackle78Facts.N681.B816
import Thrackle78Facts.N681.B817
import Thrackle78Facts.N681.B818
import Thrackle78Facts.N681.B819
import Thrackle78Facts.N681.B820
import Thrackle78Facts.N681.B821
import Thrackle78Facts.N681.B822
import Thrackle78Facts.N681.B823
import Thrackle78Facts.N681.B824
import Thrackle78Facts.N681.B825
import Thrackle78Facts.N681.B826
import Thrackle78Facts.N681.B827
import Thrackle78Facts.N681.B828
import Thrackle78Facts.N681.B829
import Thrackle78Facts.N681.B830
import Thrackle78Facts.N681.B831
import Thrackle78Facts.N681.B832
import Thrackle78Facts.N681.B833
import Thrackle78Facts.N681.B834
import Thrackle78Facts.N681.B835
import Thrackle78Facts.N681.B836
import Thrackle78Facts.N681.B837
import Thrackle78Facts.N681.B838
import Thrackle78Facts.N681.B839

open Thrackle78 Thrackle78Core

theorem T78Native.N681.group_ok_20 : ∀ j < 40, checkBFromListRX 12 lDB681.toArray T78Native.N681.fsX (T78Native.N681.orcF lDB681.toArray) (T78Native.N681.famOrcF lDB681.toArray) (T78Native.N681.adaptF lDB681.toArray) (T78Native.N681.batch (40 * 20 + j)) = true := by
  intro j hj
  interval_cases j
  exacts [T78Native.N681.batch_ok_800,
      T78Native.N681.batch_ok_801,
      T78Native.N681.batch_ok_802,
      T78Native.N681.batch_ok_803,
      T78Native.N681.batch_ok_804,
      T78Native.N681.batch_ok_805,
      T78Native.N681.batch_ok_806,
      T78Native.N681.batch_ok_807,
      T78Native.N681.batch_ok_808,
      T78Native.N681.batch_ok_809,
      T78Native.N681.batch_ok_810,
      T78Native.N681.batch_ok_811,
      T78Native.N681.batch_ok_812,
      T78Native.N681.batch_ok_813,
      T78Native.N681.batch_ok_814,
      T78Native.N681.batch_ok_815,
      T78Native.N681.batch_ok_816,
      T78Native.N681.batch_ok_817,
      T78Native.N681.batch_ok_818,
      T78Native.N681.batch_ok_819,
      T78Native.N681.batch_ok_820,
      T78Native.N681.batch_ok_821,
      T78Native.N681.batch_ok_822,
      T78Native.N681.batch_ok_823,
      T78Native.N681.batch_ok_824,
      T78Native.N681.batch_ok_825,
      T78Native.N681.batch_ok_826,
      T78Native.N681.batch_ok_827,
      T78Native.N681.batch_ok_828,
      T78Native.N681.batch_ok_829,
      T78Native.N681.batch_ok_830,
      T78Native.N681.batch_ok_831,
      T78Native.N681.batch_ok_832,
      T78Native.N681.batch_ok_833,
      T78Native.N681.batch_ok_834,
      T78Native.N681.batch_ok_835,
      T78Native.N681.batch_ok_836,
      T78Native.N681.batch_ok_837,
      T78Native.N681.batch_ok_838,
      T78Native.N681.batch_ok_839]
