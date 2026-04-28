Theory spec_arm8
Ancestors words arm8

(* ----------------- *)
(* Utility functions *)
(* ----------------- *)

Definition arm8_load_64_def:
  arm8_load_64 m a =
  (((m (a + 7w)) @@
  (((m (a + 6w)) @@
  (((m (a + 5w)) @@
  (((m (a + 4w)) @@
  (((m (a + 3w)) @@
   (((m (a + 2w)) @@
     ((m (a + 1w)) @@ (m (a + 0w))):bool[16]):bool[24])):bool[32])
    ):bool[40])):bool[48])):bool[56])):bool[64])
End

(* ------------------ *)
(* Program boundaries *)
(* ------------------ *)

Definition swap_init_addr_def:
 swap_init_addr : word64 = 0x718w
End

Definition swap_end_addr_def:
 swap_end_addr : word64 = 0x730w
End

(* -------------- *)
(* ARMv8 contract *)
(* -------------- *)

(* ==== Function max ====*)
Definition arm8_max_pre_def:
 arm8_max_pre (pre_x0:word32) (pre_x1:word32) (s:arm8_state) : bool =
  ((pre_x1 = (word_extract 31 0 (s.REG 1w))) /\
  (pre_x0 = (word_extract 31 0 (s.REG 0w))))
End

Definition arm8_max_post_def:
 arm8_max_post (pre_x0:word32) (pre_x1:word32) (st:arm8_state) : bool =
  ((((st.REG 0w) = (sw2sw pre_x0: word64)) \/ ((st.REG 0w) = (sw2sw pre_x1: word64))) /\
  ((sw2sw pre_x0: word64) <= (st.REG 0w)) /\
  ((sw2sw pre_x1: word64) <= (st.REG 0w)))
End