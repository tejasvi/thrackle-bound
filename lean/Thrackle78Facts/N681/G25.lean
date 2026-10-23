import Thrackle78Facts.N681.B1000
import Thrackle78Facts.N681.B1001
import Thrackle78Facts.N681.B1002
import Thrackle78Facts.N681.B1003
import Thrackle78Facts.N681.B1004
import Thrackle78Facts.N681.B1005
import Thrackle78Facts.N681.B1006
import Thrackle78Facts.N681.B1007
import Thrackle78Facts.N681.B1008
import Thrackle78Facts.N681.B1009
import Thrackle78Facts.N681.B1010
import Thrackle78Facts.N681.B1011
import Thrackle78Facts.N681.B1012
import Thrackle78Facts.N681.B1013
import Thrackle78Facts.N681.B1014
import Thrackle78Facts.N681.B1015
import Thrackle78Facts.N681.B1016
import Thrackle78Facts.N681.B1017
import Thrackle78Facts.N681.B1018
import Thrackle78Facts.N681.B1019
import Thrackle78Facts.N681.B1020
import Thrackle78Facts.N681.B1021
import Thrackle78Facts.N681.B1022
import Thrackle78Facts.N681.B1023
import Thrackle78Facts.N681.B1024
import Thrackle78Facts.N681.B1025
import Thrackle78Facts.N681.B1026
import Thrackle78Facts.N681.B1027
import Thrackle78Facts.N681.B1028
import Thrackle78Facts.N681.B1029
import Thrackle78Facts.N681.B1030
import Thrackle78Facts.N681.B1031
import Thrackle78Facts.N681.B1032
import Thrackle78Facts.N681.B1033
import Thrackle78Facts.N681.B1034
import Thrackle78Facts.N681.B1035
import Thrackle78Facts.N681.B1036
import Thrackle78Facts.N681.B1037
import Thrackle78Facts.N681.B1038
import Thrackle78Facts.N681.B1039

open Thrackle78 Thrackle78Core

theorem T78Native.N681.group_ok_25 : ∀ j < 40, checkBFromListRX 12 lDB681.toArray T78Native.N681.fsX (T78Native.N681.orcF lDB681.toArray) (T78Native.N681.famOrcF lDB681.toArray) (T78Native.N681.adaptF lDB681.toArray) (T78Native.N681.batch (40 * 25 + j)) = true := by
  intro j hj
  interval_cases j
  exacts [T78Native.N681.batch_ok_1000,
      T78Native.N681.batch_ok_1001,
      T78Native.N681.batch_ok_1002,
      T78Native.N681.batch_ok_1003,
      T78Native.N681.batch_ok_1004,
      T78Native.N681.batch_ok_1005,
      T78Native.N681.batch_ok_1006,
      T78Native.N681.batch_ok_1007,
      T78Native.N681.batch_ok_1008,
      T78Native.N681.batch_ok_1009,
      T78Native.N681.batch_ok_1010,
      T78Native.N681.batch_ok_1011,
      T78Native.N681.batch_ok_1012,
      T78Native.N681.batch_ok_1013,
      T78Native.N681.batch_ok_1014,
      T78Native.N681.batch_ok_1015,
      T78Native.N681.batch_ok_1016,
      T78Native.N681.batch_ok_1017,
      T78Native.N681.batch_ok_1018,
      T78Native.N681.batch_ok_1019,
      T78Native.N681.batch_ok_1020,
      T78Native.N681.batch_ok_1021,
      T78Native.N681.batch_ok_1022,
      T78Native.N681.batch_ok_1023,
      T78Native.N681.batch_ok_1024,
      T78Native.N681.batch_ok_1025,
      T78Native.N681.batch_ok_1026,
      T78Native.N681.batch_ok_1027,
      T78Native.N681.batch_ok_1028,
      T78Native.N681.batch_ok_1029,
      T78Native.N681.batch_ok_1030,
      T78Native.N681.batch_ok_1031,
      T78Native.N681.batch_ok_1032,
      T78Native.N681.batch_ok_1033,
      T78Native.N681.batch_ok_1034,
      T78Native.N681.batch_ok_1035,
      T78Native.N681.batch_ok_1036,
      T78Native.N681.batch_ok_1037,
      T78Native.N681.batch_ok_1038,
      T78Native.N681.batch_ok_1039]
